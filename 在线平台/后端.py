from flask import Flask, request, send_from_directory, jsonify
import os
import subprocess
from werkzeug.utils import secure_filename
from flask_cors import CORS

app = Flask(__name__)
CORS(app)

UPLOAD_FOLDER = '/home/cishu/build/bin'
ALLOWED_EXTENSIONS = {'c', 'cc', 'cpp'}
app.config['MAX_CONTENT_LENGTH'] = 1 * 1024 * 1024

def allowed_file(filename):
    return '.' in filename and filename.rsplit('.', 1)[1].lower() in ALLOWED_EXTENSIONS

@app.route('/upload', methods=['POST'])
def upload_file():
    if 'file' not in request.files:
        return jsonify({'message': 'No file part'}), 400
    file = request.files['file']
    if file.filename == '':
        return jsonify({'message': 'No selected file'}), 400
    if file and allowed_file(file.filename):
        filename = secure_filename(file.filename)
        file_path = os.path.join(UPLOAD_FOLDER, filename)
        file.save(file_path)
        
        option = request.form.get('option', 'none').lstrip('-')
        if option not in ['fla', 'bcf', 'sub', 'sobf', 'vrobf']:
            return jsonify({'message': 'Invalid option'}), 400

        output_filename = os.path.splitext(filename)[0] + '_' + option
        output_file_path = os.path.join(UPLOAD_FOLDER, output_filename)
        command = ['./clang', '-mllvm', '-' + option, file_path, '-o', output_file_path]

        if filename.endswith('.cpp'):
            command.append('-lstdc++')
        
        try:
            subprocess.run(command, check=True)
            response = send_from_directory(UPLOAD_FOLDER, output_filename, as_attachment=True)
            os.remove(file_path)
            os.remove(output_file_path)
            return response, 200
        except subprocess.CalledProcessError:
            os.remove(file_path)
            if os.path.exists(output_file_path):
                os.remove(output_file_path)
            return jsonify({'message': 'Compilation failed'}), 500
    else:
        return jsonify({'message': 'Invalid file type or size'}), 400

if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)

